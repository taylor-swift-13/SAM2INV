int main1(int b,int n){
  int h, l, v;

  h=b;
  l=1;
  v=h;

  while (l<=h/3) {
      v = v+2;
      if (l+5<=h+h) {
          v = v*2;
      }
      else {
          v = v*v+v;
      }
  }

}
