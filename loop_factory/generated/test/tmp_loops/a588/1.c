int main1(int m,int q){
  int l, i, v, k;

  l=(m%14)+19;
  i=l;
  v=q;
  k=m;

  while (i>0) {
      v = v+1;
      k = k-1;
  }

  while (i<k) {
      i = i+1;
  }

}
