int main1(int k,int n){
  int h, j, v, b;

  h=31;
  j=0;
  v=-5;
  b=k;

  while (j<=h-2) {
      v = v+b+b;
      v = v+1;
      if ((j%8)==0) {
          v = v+b;
      }
      j = j+2;
  }

}
