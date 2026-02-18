int main1(int a,int m,int p,int q){
  int l, i, v;

  l=(a%12)+20;
  i=0;
  v=0;

  while (i<l) {
      if ((i%5)==0) {
          v = v*v;
      }
      else {
          v = v+i;
      }
      v = v+v;
      i = i+1;
  }

}
