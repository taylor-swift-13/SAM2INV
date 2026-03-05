int main1(int c,int n){
  int qn0, iq1, v0;

  qn0=(c%37)+12;
  iq1=2;
  v0=0;

  while (iq1<qn0) {
      v0++;
      if (v0>=5) {
          v0 = v0 - 5;
          v0++;
      }
      iq1 = iq1 + 1;
  }

}
