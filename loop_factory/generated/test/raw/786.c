int main1(){
  int ck, c, gh, h3, fp;

  ck=1;
  c=-2;
  gh=0;
  h3=-3;
  fp=c;

  while (1) {
      if (!(c<=ck-1)) {
          break;
      }
      h3 = h3*h3+gh;
      gh = gh%6;
      gh = gh*fp;
      c = c + 1;
  }

}
