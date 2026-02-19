int main1(int k,int p){
  int l, i, v;

  l=p-2;
  i=l;
  v=i;

  while (i>0) {
      i = i-1;
  }

  while (i<l) {
      v = v+v;
      v = v+1;
      i = i*2;
  }

}
