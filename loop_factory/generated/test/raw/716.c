int main1(){
  int l, sbrt, vf, tv, gs0;

  l=80;
  sbrt=4;
  vf=(1%40)+2;
  tv=0;
  gs0=5;

  while (vf!=tv) {
      tv = vf;
      vf = (vf+l/vf)/2;
      gs0 = gs0 + sbrt;
  }

}
