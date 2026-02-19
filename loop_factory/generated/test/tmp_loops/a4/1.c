int main1(int a,int k){
  int l, i, v, c;

  l=(a%16)+9;
  i=l;
  v=i;
  c=l;

  while (i>0) {
      c = c+c;
      c = c+v;
      i = i-1;
  }

  while (i>0) {
      i = i-1;
  }

}
