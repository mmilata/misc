#ifndef FB_ERROR_H
#define FB_ERROR_H

#include <exception>
#include <string>

class Error : public std::exception {
	public:
		Error(const char *data) : fData(data) {};
		virtual ~Error() throw() {};
		virtual const char* what() const throw() {return fData.c_str();};

	private:
		std::string fData;
};
		
#endif
