int main131(int a,int k,int p){
  int l, o, v;

  l=a;
  o=1;
  v=o;

  while (o*2<=l) {
      v = v+4;
      v = v*v+v;
      if (v+3<l) {
          v = v%2;
      }
      else {
          v = v%9;
      }
      v = v%6;
  }

  while (l+3<=o) {
      v = v+2;
      v = v*v;
  }

}
