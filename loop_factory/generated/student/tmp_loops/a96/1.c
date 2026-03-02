int main1(int a,int b){
  int c, i, d;

  c=b+4;
  i=c;
  d=i;

  while (i-4>=0) {
      d = d+4;
      if (d+1<c) {
          d = d+d;
      }
  }

}
