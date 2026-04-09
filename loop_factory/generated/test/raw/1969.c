int main1(int q){
  int s, gnwb, tx, cra;

  s=q;
  gnwb=0;
  tx=0;
  cra=q;

  while (1) {
      if (!(gnwb < s)) {
          break;
      }
      tx = tx + 2*gnwb + 1;
      cra += tx;
      gnwb++;
  }

}
