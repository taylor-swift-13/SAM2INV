int main1(int b,int k){
  int q, r, h, v;

  q=k;
  r=1;
  h=q;
  v=b;

  while (r<q) {
      v = v+h;
      h = h*h+h;
      h = h%7;
  }

}
