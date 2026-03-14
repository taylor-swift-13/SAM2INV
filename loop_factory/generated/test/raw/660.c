int main1(int l){
  int tn, bns, z3, w;

  tn=(l%19)+13;
  bns=tn;
  z3=4;
  w=0;

  while (w<tn) {
      w += 1;
      z3 += l;
  }

  while (1) {
      tn++;
      if (tn>=bns) {
          break;
      }
  }

}
