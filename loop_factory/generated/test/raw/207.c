int main1(int c,int f){
  int kzeq, y, nsx3, q1, x1;

  kzeq=f+11;
  y=4;
  nsx3=0;
  q1=3;
  x1=f;

  while (nsx3<=kzeq-1) {
      q1 += nsx3;
      x1 = x1 + y;
      nsx3 = nsx3 + 1;
  }

  while (y<kzeq) {
      q1 = kzeq-y;
      y++;
      c += q1;
  }

}
