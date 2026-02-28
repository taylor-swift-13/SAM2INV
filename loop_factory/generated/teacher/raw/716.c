int main1(int a,int b,int m,int q){
  int t, i, f;

  t=(q%13)+13;
  i=0;
  f=6;

  while (1) {
      f = f+3;
      if (m<t+5) {
          f = f-f;
      }
      f = f+i;
  }

}
