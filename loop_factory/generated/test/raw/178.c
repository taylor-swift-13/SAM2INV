int main1(int t,int k){
  int qo8, me, q, kdxc, l6, mo;

  qo8=k*5;
  me=qo8;
  q=15;
  kdxc=0;
  l6=1;
  mo=0;

  while (1) {
      if (!(q>0&&me<qo8)) {
          break;
      }
      if (q<=l6) {
          mo = q;
      }
      else {
          mo = l6;
      }
      kdxc += mo;
      l6 = l6 + 1;
      q -= mo;
      me = me + 1;
  }

}
