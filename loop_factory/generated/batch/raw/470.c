int main1(int a,int n){
  int b, c, j;

  b=(n%21)+4;
  c=0;
  j=c;

  while (1) {
      j = j+2;
      if (j+1<b) {
          j = j+j;
      }
  }

}
