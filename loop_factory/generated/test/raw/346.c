int main1(){
  int hnz, vs, nbs7, o1f;

  hnz=1;
  vs=4;
  nbs7=0;
  o1f=0;

  while (nbs7<hnz) {
      vs += 1;
      nbs7 = nbs7 + 1;
      o1f += hnz;
  }

  while (nbs7<hnz) {
      o1f++;
      nbs7 = nbs7 + 1;
      o1f = o1f + vs;
  }

}
