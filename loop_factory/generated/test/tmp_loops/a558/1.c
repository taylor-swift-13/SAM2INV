int main1(int a,int q){
  int l, i, v, w;

  l=(q%9)+5;
  i=l;
  v=q;
  w=5;

  while (i>0) {
      v = v+1;
      w = w+v;
      i = i-1;
  }

  while (l<v) {
      l = l*3;
  }

}
