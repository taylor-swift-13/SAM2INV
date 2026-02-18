int main1(int a,int m,int p,int q){
  int l, i, v, h;

  l=(a%9)+15;
  i=0;
  v=a;
  h=i;

  while (i<l) {
      h = h+h;
      h = h+v;
      i = i+1;
  }

}
