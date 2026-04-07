int main1(){
  int dy, s, z, igh, b;

  dy=(1%26)+8;
  s=dy;
  z=-1;
  igh=dy;
  b=s;

  while (s>3) {
      igh = igh + 1;
      b = b*3+(igh%5)+1;
      z = igh*igh;
      s = 3;
  }

}
