int main1(int b,int n){
  int l, i, v;

  l=n+23;
  i=l;
  v=-8;

  while (i>0) {
      v = v+i;
      if ((i%6)==0) {
          v = v*v;
      }
      i = i-1;
  }

}
