int main1(){
  int p, bpq, a;

  p=(1%18)+5;
  bpq=(1%15)+3;
  a=p;

  while (1) {
      if (!(p!=0)) {
          break;
      }
      bpq = bpq - 1;
      p -= 1;
      a = a + bpq;
  }

}
