int main1(int b,int m){
  int c, t, v;

  c=b;
  t=0;
  v=b;

  while (t<=c-2) {
      v = v+3;
      if (v+1<c) {
          v = v+v;
      }
      else {
          v = v+t;
      }
      if ((t%7)==0) {
          v = v+v;
      }
  }

}
