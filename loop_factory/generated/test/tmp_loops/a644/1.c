int main1(int k,int p){
  int l, i, v, c;

  l=(p%24)+5;
  i=l;
  v=i;
  c=-1;

  while (i>0) {
      v = v+1;
      i = i-1;
  }

  while (c<l) {
      i = i+1;
      v = v+i;
      c = c+1;
  }

}
