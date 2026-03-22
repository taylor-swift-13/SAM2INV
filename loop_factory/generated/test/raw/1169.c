int main1(){
  int x, ak, ifd, rb, w;

  x=1*2;
  ak=0;
  ifd=1;
  rb=1;
  w=0;

  while (1) {
      if (!(ifd<=x)) {
          break;
      }
      ak = ak + 1;
      rb += 2;
      w = w+rb+ak;
      ifd += rb;
  }

}
