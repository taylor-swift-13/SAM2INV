int main1(int i,int c){
  int hm, vs, k7, s, v;

  hm=i+11;
  vs=0;
  k7=1;
  s=6;
  v=0;

  while (1) {
      if (!(v<=hm)) {
          break;
      }
      vs += k7;
      v++;
      k7 = k7 + s;
      s += 6;
      c = c + s;
      i = i+s+k7;
  }

}
