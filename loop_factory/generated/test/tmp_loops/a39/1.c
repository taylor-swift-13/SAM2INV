int main1(int b,int m){
  int l, i, v, w;

  l=61;
  i=l;
  v=m;
  w=i;

  while (i>0) {
      v = v+1;
      w = w-1;
      v = v+3;
  }

  while (i>0) {
      w = w*3;
      v = v/3;
      v = v+v;
  }

}
