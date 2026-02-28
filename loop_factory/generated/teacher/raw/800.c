int main1(int a,int b){
  int n, f, v;

  n=(b%33)+13;
  f=0;
  v=3;

  while (1) {
      v = v+3;
      if ((f%4)==0) {
          v = v-v;
      }
  }

}
