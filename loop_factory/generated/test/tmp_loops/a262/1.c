int main1(int p,int q){
  int l, i, v, o;

  l=74;
  i=l;
  v=i;
  o=q;

  while (i>0) {
      o = o+o;
      i = i-1;
  }

  while (o>0) {
      i = i*2;
      v = v/2;
  }

}
