int main1(int r,int b){
  int ue, tq, j, qp, c, el;

  ue=(r%30)+16;
  tq=ue+3;
  j=0;
  qp=(r%28)+10;
  c=b;
  el=0;

  while (qp>j) {
      qp -= j;
      j++;
      r += 2;
      el = el + tq;
      c = c+(j%9);
  }

  while (1) {
      j++;
      if (j>=tq) {
          break;
      }
  }

}
