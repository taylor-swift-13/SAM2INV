int main1(int a,int k,int n,int p){
  int l, i, v;

  l=a+13;
  i=0;
  v=k;

  while (i<l) {
      if ((i%5)==0) {
          v = v+5;
      }
      else {
          v = v+1;
      }
      i = i+1;
  }

}
