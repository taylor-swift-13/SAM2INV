int main1(int l,int q){
  int ji, j137, z, ez, p, afow;

  ji=64;
  j137=ji;
  z=0;
  ez=0;
  p=0;
  afow=(l%18)+5;

  while (1) {
      if (!(afow>=1)) {
          break;
      }
      z = z+l*l;
      afow--;
      ez = ez+q*q;
      p = p+l*q;
      l = l + j137;
  }

}
