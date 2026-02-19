int main1(int b,int p){
  int l, i, v, f;

  l=b;
  i=0;
  v=p;
  f=i;

  while (i<l) {
      v = v+1;
      i = i+1;
  }

  while (l>0) {
      f = f+1;
      f = f-f;
      l = l-1;
  }

}
