int main1(int a,int k,int p){
  int l, i, v, u, x;

  l=58;
  i=0;
  v=i;
  u=l;
  x=l;

  while (i<l) {
      u = u+x;
      x = x+v;
      if ((i%6)==0) {
          u = u+5;
      }
      i = i+1;
  }

}
