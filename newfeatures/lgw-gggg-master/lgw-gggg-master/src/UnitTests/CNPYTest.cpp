#include <vector>

#include <cnpy/cnpy.h>

int main() {
	std::vector<uint32_t> a(778126008);
	std::vector<uint32_t> b(389063004);

	std::string output("/tmp/tmparray");
	cnpy::npz_save(output, "a", &a[0], {a.size()}, "w");
	cnpy::npz_save(output, "b", &b[0], {b.size()}, "a");

	std::string zipName("/tmp/tmparrayFiles");
	// for (int i = 0; i < 4000; ++i) {
	//     std::vector<uint32_t> arr(1000000);
	//     std::string outputName = "arr_" + std::to_string(i);
	//     std::cout << "Adding file " << outputName << std::endl;
	//     cnpy::npz_save(zipName, outputName, &arr[0], {arr.size()}, (i=0)?
	//     "w": "a");
	// }

	libzip::archive zip(zipName, ZIP_TRUNCATE | ZIP_CREATE);
	for (int i = 0; i < 5000; ++i) {
		std::vector<uint32_t> arr(250000);
		std::string outputName = "arr_" + std::to_string(i);
		std::cout << "Adding file " << i << std::endl;
		cnpy::add_npy_to_zip(zip, outputName, &arr[0], {arr.size()});
	}
}
