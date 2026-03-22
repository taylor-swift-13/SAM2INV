int main1(int j,int d){
  int qg, b, qh;

  qg=0;
  b=(j%28)+10;
  qh=3;

  while (1) {
      if (!(b>qg)) {
          break;
      }
      b -= qg;
      qg = (1)+(qg);
      j = j+(qg%4);
      d = d*d+qh;
  }

}
