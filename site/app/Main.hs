{-# LANGUAGE OverloadedStrings #-}
import Hakyll
import Data.Maybe (fromMaybe)
import Data.List (isPrefixOf, isSuffixOf)
import System.FilePath (takeFileName)
import qualified Text.Pandoc as PD


config :: Configuration
config =
  defaultConfiguration
    { destinationDirectory = "dist"
    , ignoreFile = ignoreFile'
    , previewHost = "127.0.0.1"
    , previewPort = 8000
    , providerDirectory = "pages"
    , storeDirectory = "site/_cache"
    , tmpDirectory = "site/_tmp"
    }
  where
    ignoreFile' path
      | "."    `isPrefixOf` fileName = False
      | "#"    `isPrefixOf` fileName = True
      | "~"    `isSuffixOf` fileName = True
      | ".swp" `isSuffixOf` fileName = True
      | otherwise = False
      where
        fileName = takeFileName path

pandocCompiler' = pandocCompilerWith defaultHakyllReaderOptions
    defaultHakyllWriterOptions

main :: IO ()
main = hakyllWith config $ do

  match "templates/*" $ compile templateBodyCompiler

  match ( "css/*" .||. "css/**/*") $ do
        route  $ gsubRoute "css/" (const "") `composeRoutes` setExtension "css"
        compile compressCssCompiler

  match "posts/*" $ do
      route $ setExtension "html" -- blogRoutePrefix $ gsubRoute "pages/" (const "") `composeRoutes` setExtension "html"
      compile $ do
        -- tpl <- loadBody "templates/post.html"
        pandocCompiler'
          -- >>= loadAndApplyTemplate "templates/page-body.html" defaultContext
          >>= loadAndApplyTemplate "templates/default.html" postCtx
          >>= relativizeUrls

  match "index.html" $ do
    route idRoute
    compile $ do
      -- posts <- recentFirst =<< loadAll "posts/*" -- issue with UTC time here
      posts <- loadAll "posts/*"


      let indexCtx =
              listField "posts" postCtx (return posts)
              <> constField "root" mySiteRoot
              <> constField "feedTitle" myFeedTitle
              <> constField "siteName" mySiteName
              <> defaultContext

      getResourceBody
          >>= applyAsTemplate indexCtx
          >>= loadAndApplyTemplate "templates/default.html" indexCtx
          >>= relativizeUrls


mySiteName :: String
mySiteName = "Samuel Toth"

mySiteRoot :: String
mySiteRoot = "https://samtoth.github.io/blog"

myFeedTitle :: String
myFeedTitle = "Articles"

myFeedDescription :: String
myFeedDescription = "My Site Description"

myFeedAuthorName :: String
myFeedAuthorName = "Samuel Toth"

myFeedAuthorEmail :: String
myFeedAuthorEmail = "sam@toth.co.uk"

myFeedRoot :: String
myFeedRoot = mySiteRoot



feedCtx :: Context String
feedCtx =
  titleCtx
    <> postCtx
    <> bodyField "description"

postCtx :: Context String
postCtx =
  constField "root" mySiteRoot
    <> constField "feedTitle" myFeedTitle
    <> constField "siteName" mySiteName
    <> dateField "date" "%Y-%m-%d"
    -- <> constField "desc" "Uh oh"
    <> defaultContext

titleCtx :: Context String
titleCtx =
  field "title" updatedTitle


replaceAmp :: String -> String
replaceAmp =
  replaceAll "&" (const "&amp;")

replaceTitleAmp :: Metadata -> String
replaceTitleAmp =
  replaceAmp . safeTitle

safeTitle :: Metadata -> String
safeTitle =
  fromMaybe "no title" . lookupString "title"

updatedTitle :: Item a -> Compiler String
updatedTitle =
  fmap replaceTitleAmp . getMetadata . itemIdentifier