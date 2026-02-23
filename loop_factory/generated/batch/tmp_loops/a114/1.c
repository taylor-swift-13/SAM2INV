int main1(int a,int p){
  int h, o, v;

  h=a+6;
  o=h;
  v=a;

  while (o>1) {
      if (v+2<h) {
          v = v*v+v;
      }
      o = o/2;
  }

}
