int main1(){
  int het, rmv, dq, n;

  het=1*2;
  rmv=0;
  dq=(1%28)+10;
  n=het;

  while (1) {
      if (!(dq>rmv)) {
          break;
      }
      dq = dq - rmv;
      n = n + het;
      rmv = (1)+(rmv);
  }

}
