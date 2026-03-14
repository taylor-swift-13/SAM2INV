int main1(){
  int k, uf, v, np, l1xk;

  k=1;
  uf=1;
  v=0;
  np=0;
  l1xk=8;

  while (1) {
      if (!(v<=k-1)) {
          break;
      }
      np += v;
      l1xk = l1xk + uf;
      v++;
  }

  while (1) {
      if (!(l1xk>=1)) {
          break;
      }
      l1xk--;
  }

}
