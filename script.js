function TypeWrite(){
    var typewriteTextDiv = document.querySelector("#front");
    var typewriteDiv = document.querySelector("#first-typewrite");
    var words = ["programmer", "musician","banjo player", "history lover","Random Person"];
    var index = 0;
    setTimeout(() => {
        setInterval(changeVocab,3500);
        console.log("hello");
    }, 1500);

    const changeVocab = ()=>{
        console.log(words[index])

        typewriteTextDiv.style.animation = "change-word-animation 3.5s steps(12,end) infinite";
        console.log(typewriteTextDiv)
         typewriteTextDiv.innerHTML = `Hello, Nice to meet you, I'm a ${words[index]}`;
         typewriteDiv.childNodes[0].nodeValue = `Hello, Nice to meet you, I'm a ${words[index]}`;
         index++;
         if(index>=words.length){
             index= 0;
         }
    }
}
TypeWrite();