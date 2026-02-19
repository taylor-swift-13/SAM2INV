int main1(int k,int q){
  int l, i, v, a;

  l=(q%27)+16;
  i=l;
  v=l;
  a=l;

  while (i>0) {
      v = v+4;
      a = a+3;
      i = i/2;
  }

  while (a<l) {
      a = a+4;
  }

}
