int main1(int a,int b){
  int l, i, v, r;

  l=b-3;
  i=l;
  v=b;
  r=i;

  while (i>0) {
      v = v+1;
      r = r+1;
  }

  while (i<v) {
      r = r+1;
      i = i+1;
  }

}
