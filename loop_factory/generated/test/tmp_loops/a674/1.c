int main1(int a,int p){
  int l, i, v;

  l=p;
  i=l;
  v=1;

  while (i>0) {
      v = v+3;
      v = v+v;
      i = i-1;
  }

  while (i<v) {
      i = i+1;
  }

}
