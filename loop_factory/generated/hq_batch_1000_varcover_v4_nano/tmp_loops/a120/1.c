int main1(int a,int b,int p,int q){
  int l, i, v, f, w, z, e;

  l=q-1;
  i=0;
  v=(q%60)+60;
  f=(q%9)+2;
  w=0;
  z=0;
  e=b;

  while (v>f*w+z) {
      if (z==f-1) {
          z = 0;
          w = w+1;
      }
      else {
          z = z+1;
      }
      v = v*2;
  }

}
