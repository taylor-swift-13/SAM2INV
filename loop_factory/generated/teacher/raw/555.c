int main1(int p,int q){
  int e, l, j, v;

  e=q+9;
  l=1;
  j=p;
  v=q;

  while (l<e) {
      j = j+v;
      v = v+v;
      v = v+2;
      l = l+1;
  }

}
