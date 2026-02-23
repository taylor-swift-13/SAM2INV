int main1(int a,int p){
  int s, q, m, d;

  s=(p%20)+5;
  q=0;
  m=1;
  d=q;

  while (q+4<=s) {
      if (m+4<=s) {
          m = m+4;
      }
      else {
          m = s;
      }
      m = m+1;
      d = d-1;
  }

}
