import yaml
from yaml.loader import SafeLoader
import io
import os
import hashlib
from datetime import datetime
from argparse import ArgumentParser

spdx_version = 'SPDX-2.2'
data_license = 'CC0-1.0'
sbom_creator = 'Amazon Web Services'
sbom_namespace = 'https://github.com/amazon-freertos/pkcs11/blob/9304ef6842d08d881ccd1daa8d3a428f3a9671ee/corePKCS.spdx'
manifest_path = '/Users/linrjack/Desktop/workplace/corePKCS11/manifest.yml'
dependency_path = '/Users/linrjack/Desktop/workplace/corePKCS11/source/dependency/3rdparty'
url = 'https://github.com/FreeRTOS/corePKCS11'
REPO_PATH = ' '
    
def hash_sha1(file_path):
    BLOCKSIZE = 65536
    hasher = hashlib.sha1()
    with open(file_path, 'rb') as afile:
        buf = afile.read(BLOCKSIZE)
        while len(buf) > 0:
            hasher.update(buf)
            buf = afile.read(BLOCKSIZE)
    return hasher.hexdigest()

def package_hash(file_list):
    sorted(file_list)
    h = hashlib.sha1("".join(file_list).encode())
    return h.hexdigest()

def file_writer(o, filepath, filename, sha1, license, copyright='NOASSERTION', comment='NOASSERTION'):
    o.write('FileName: '+ filepath + '\n')
    o.write('SPDXID: SPDXRef-File-'+ filename + '\n')
    o.write('FileChecksum: SHA1: '+ hash_sha1(filepath) + '\n')
    o.write('LicenseConcluded: '+ license + '\n')
    o.write('FileCopyrightText: '+ copyright + '\n')
    o.write('FileComment: '+ comment + '\n')
    o.write('\n')
    
    
def pacakge_writer(o, packageName, version, url, license, ver_code, file_analyzed=True, 
                   copyright='NOASSERTION', summary='NOASSERTION', description='NOASSERTION'):
    o.write('PackageName: '+ packageName + '\n')
    o.write('SPDXID: SPDXRef-Package-'+ packageName + '\n')
    o.write('PackageVersion: '+ version + '\n')
    o.write('PackageDownloadLocation: '+ url + '\n')
    o.write('PackageLicenseConcluded: '+ license + '\n')
    o.write('FilesAnalyzed: '+ str(file_analyzed) + '\n')
    o.write('PackageVerificationCode: '+ ver_code + '\n')
    o.write('PackageCopyrightText: '+ copyright + '\n')
    o.write('PackageSummary: '+ summary + '\n')
    o.write('PackageDescription: '+ description + '\n')
    o.write('\n')

def doc_writer(o, version, license, name, namespace, creator, creator_comment='NOASSERTION', 
               doc_comment='NOASSERTION'):
    today = datetime.now()
    o.write('SPDXVersion: ' + version + '\n')
    o.write('DataLicense: ' + license + '\n')
    o.write('SPDXID: SPDXRef-DOCUMENT' + '\n')
    o.write('DocumentName: ' + name + '\n')
    o.write('DocumentNamespace: ' + namespace + '\n')
    o.write('Creator: ' + creator + '\n')
    o.write('Created: ' + today.isoformat()[:-7] + 'Z\n')
    o.write('CreatorComment: ' + creator_comment + '\n')
    o.write('DocumentComment: ' + doc_comment + '\n')
    o.write('\n')
    
    
def scan_pkcs():
    dependency_path = os.path.join(REPO_PATH, 'source/dependency/3rdparty')
    o = io.StringIO() #open('tcp.spdx', 'w')
    buffer3rd = {}
    dependency_info = {}
    total_file_list = []
    dependency_file_list = {}
    with open(os.path.join(REPO_PATH, 'manifest.yml')) as f:
        manifest = yaml.load(f, Loader=SafeLoader)
    root_license = manifest['license']
    
    #delete later
    manifest['dependencies'][0]['license'] = 'Apache License 2.0'
    manifest['dependencies'][1]['license'] = 'OASIS License'
    #manifest['dependencies'][0]['copyright'] = 'NOASSERTION'
    #manifest['dependencies'][1]['copyright'] = 'By using this GitHub code repository, you agree to comply with \
#the OASIS license agreement referred in this link. (https://www.oasis-open.org/cla/)'
    
    for dependency in manifest['dependencies']:
        buffer3rd[dependency['name']] = io.StringIO()
        dependency_info[dependency['name']] = dependency
        
    for subdir, dirs, files in os.walk(os.path.join(REPO_PATH, 'source')):
        if 'dependency' in subdir:
            continue
        for file in files:
            if file.endswith('.spdx'):
                continue
            filepath = os.path.join(subdir, file)
            file_checksum = hash_sha1(filepath)
            if file.endswith('.c'):
                file_writer(o, filepath, file, file_checksum, root_license)
            total_file_list.append(file_checksum)
    
                        
    for library in os.listdir(dependency_path):
        if library.startswith('.'):
            continue
        library_lic = root_license
        try: 
            buffer = buffer3rd[library]
            library_lic = dependency_info[library]['license']
            #copyright = dependency_info[library]['copyright']
            dependency_file_list[library] = []
            temp_list = dependency_file_list[library]
        except:
            buffer = o
            temp_list = []
            

        for subdir, dirs, files in os.walk(os.path.join(dependency_path, library)):
            for file in files:
                filepath = os.path.join(subdir, file)
                file_checksum = hash_sha1(filepath)
                if file.endswith('.c'):
                    file_writer(buffer, filepath, file, file_checksum, library_lic)
                total_file_list.append(file_checksum)
                temp_list.append(file_checksum)
    

    output = open('corePKCS11.spdx', 'w')
    doc_writer(output, spdx_version, data_license, manifest['name'], sbom_namespace, sbom_creator)
    pacakge_writer(output, manifest['name'], manifest['version'], url, root_license, package_hash(total_file_list), description=manifest['description'])
    output.write(o.getvalue())
    #print packages
    for name, info in dependency_info.items():
        if len(dependency_file_list[name]) == 0:
            analyzed = False
        pacakge_writer(output, name, info['version'], info['repository']['url'], info['license'], package_hash(dependency_file_list[name]))
        output.write(buffer3rd[name].getvalue())
    
    #print relationships
    for dependency in dependency_info.keys():
        output.write('Relationship: SPDXRef-Package-' + manifest['name'] + ' DEPENDS_ON SPDXRef-Package-' + dependency + '\n')



if __name__ == "__main__":
    parser = ArgumentParser(description='SBOM generator')
    parser.add_argument('--repo-root-path',
                        type=str,
                        required=None,
                        default=os.getcwd(),
                        help='Path to the repository root.')
    args = parser.parse_args()
    REPO_PATH = os.path.abspath(args.repo_root_path)
    scan_pkcs()

