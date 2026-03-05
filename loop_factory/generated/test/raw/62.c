int main1(int m,int j){
  int e, gl6, grc;

  e=(m%34)+12;
  gl6=3;
  grc=-8;

  while (gl6<e) {
      grc += 2;
      grc -= 2;
      j += grc;
  }

}
