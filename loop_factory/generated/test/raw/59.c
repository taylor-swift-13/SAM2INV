int main1(int q){
  int z, nc, wa, xv;

  z=q;
  nc=0;
  wa=0;
  xv=6;

  while (nc<z&&xv>0) {
      nc += 1;
      wa += xv;
      q = q + nc;
      xv -= 1;
  }

}
