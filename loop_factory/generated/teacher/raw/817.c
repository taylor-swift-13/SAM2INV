int main1(int b,int p){
  int u, w, v, f;

  u=b;
  w=2;
  v=-5;
  f=2;

  while (1) {
      v = v+1;
      f = f+v;
      v = u+w;
      f = f+v;
      v = v+w;
      w = w+1;
  }

}
