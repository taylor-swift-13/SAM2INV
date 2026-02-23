int main1(int a,int p){
  int h, o, v, l, g;

  h=44;
  o=0;
  v=3;
  l=h;
  g=o;

  while (o+3<=h) {
      v = v+1;
      l = l+v;
      if (h<a+5) {
          l = l+6;
      }
      o = o+3;
  }

}
