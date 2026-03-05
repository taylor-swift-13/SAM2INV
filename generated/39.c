int main39(int b,int x,int m){
  int oam, z, qo, vcx, ak, i;

  oam=(x%28)+16;
  z=5;
  qo=0;
  vcx=0;
  ak=0;
  i=oam;

  while (ak<=oam-1) {
      qo += z;
      ak = ak + 1;
      vcx += qo;
      z = z;
      i = i*4+(z%3)+3;
      b += z;
  }

}
