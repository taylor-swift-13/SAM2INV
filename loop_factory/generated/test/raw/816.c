int main1(int b,int o){
  int byr, k7, gl, ln;

  byr=o*3;
  k7=0;
  gl=-6;
  ln=0;

  while (1) {
      if (!(k7+1<=byr)) {
          break;
      }
      ln = ln+gl*k7;
      byr = (k7+1)-1;
  }

}
