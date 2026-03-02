int main1(int k,int p){
  int d, z, v, o;

  d=(p%21)+12;
  z=0;
  v=-4;
  o=z;

  while (z<=d-1) {
      o = o+1;
      v = o*o;
      v = v+o;
      o = o+o;
  }

}
