int main1(int a,int k,int m,int q){
  int l, i, v, h, w, c;

  l=(m%29)+17;
  i=0;
  v=m;
  h=k;
  w=l;
  c=m;

  while (i<l) {
      v = v+1;
      h = h-1;
      w = w+6;
      if (c+3<l) {
          w = w+h;
      }
      else {
          v = v+1;
      }
      c = h-c;
      h = v-h;
      i = i+1;
  }

}
