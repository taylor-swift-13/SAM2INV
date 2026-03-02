int main1(int m,int n){
  int j, b, v;

  j=m+3;
  b=0;
  v=-4;

  while (1) {
      v = v+2;
      v = v+v;
      if ((b%7)==0) {
          v = v-v;
      }
  }

}
