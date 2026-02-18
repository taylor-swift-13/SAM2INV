int main1(int a,int k,int p,int q){
  int l, i, v, y;

  l=23;
  i=l;
  v=a;
  y=k;

  while (i>0) {
      v = v+y+y;
      v = v+1;
      y = y+1;
      if ((i%7)==0) {
          v = v+1;
      }
      i = i-1;
  }

}
