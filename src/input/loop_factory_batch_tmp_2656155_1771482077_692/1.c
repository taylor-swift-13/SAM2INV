int main1(int p,int q){
  int l, i, v;

  l=q-10;
  i=l;
  v=p;

  while (i>0) {
      v = v+v;
      i = i-1;
  }

  while (v>0) {
      i = i+1;
      i = i+i;
      v = v/2;
  }

}
