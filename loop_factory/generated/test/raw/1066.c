int main1(int k){
  int odt, k4dg, ncc, rd, b89, xp;

  odt=k*4;
  k4dg=1;
  ncc=0;
  rd=0;
  b89=k;
  xp=-1;

  while (rd<odt) {
      ncc = ncc + k;
      b89 += k4dg;
      rd++;
  }

  while (1) {
      if (!(xp>=1)) {
          break;
      }
      b89 = b89+rd*xp;
      rd = rd + b89;
      xp = 0;
  }

}
